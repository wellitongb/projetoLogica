/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package cpu;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author wellitongb
 */
public class CriarLog3 {
    private final File diretorio = new File("."); 
    private FileWriter arquivo;
    private PrintWriter output;
    private final String nome;
    /**
     *Método construtor da classe CriarLog1.
     * @param typeLog Representa o nome do algoritmo usado para criar o log.
     */
    public CriarLog3(String typeLog){
        openFile(typeLog);
        this.nome = typeLog;
        this.output.println("/*********************************");
        this.output.println("* Componentes do Grupo: ");
        this.output.println("* ELÍSIO BRENO GARCIA CARDOSO");
        this.output.println("* JOSÉ WELLITON NUNES JUNIOR");
        this.output.println("* MOISÉS CAVALCANTE FERNANDES");
        this.output.println("* VICTOR SANTIAGO VALENTE");
        this.output.println("**********************************/");
    }
    private void openFile(String typeLog){
        try{
            this.arquivo = new FileWriter(this.diretorio.getAbsolutePath().substring(0, this.diretorio.getAbsolutePath().length() - 1).concat(typeLog + " - LOG3.log"));
            this.output = new PrintWriter(this.arquivo);
        }
        catch (IOException ex) {
            System.out.println("Erro ao criar arquivo");
            Logger.getLogger(CriarLog1.class.getName()).log(Level.SEVERE, null, ex);
        }   
    }
    /**
     * Método responsável por fechar o arquivo de log aberto.
     */
    public void close(){
        this.output.close();
    }
    /**
     * Método que imprimi as informações do processo exigidas para o primeiro LOG.
     * @param filas Representa as filas de PRONTO,ESPERA,FINALIZADO.
     * @param timeSystem Representa o tempo do sistema.
     * @param executionTimeTotal
     * @throws NullPointerException Caso filas seja nulo.
     * @throws Error Caso o tamanho de filas seja diferente de 3.
     */
    public void print(ArrayList<ArrayList<Processo>> filas, int timeSystem, int executionTimeTotal){
        if(filas == null){
            throw new NullPointerException("Não foi passado as filas exigidas para impressão");
        }
        if(filas.size() != 3){
            throw new Error("Não foi passado o numero de filas exigidas para impressão");
        }
        else{
            this.output.println("Algoritmo de escalonamento usado: " + this.nome);
            this.output.println("Valor atual do Ciclo de CPU: " + timeSystem);
            int sumTimeExecutionGeral = 0, sumTimeWait = 0, sumTimeTurnaround = 0;
            for(Processo element: filas.get(2)){
                sumTimeExecutionGeral = sumTimeExecutionGeral + element.getTimeExecutionGeral();
                sumTimeWait = sumTimeWait + element.getIOserviceTime();
                sumTimeTurnaround = sumTimeTurnaround + element.getLifeTime();
            }
            this.output.println("Tempo médio de Processamento: " + (sumTimeExecutionGeral/filas.get(2).size()));
            this.output.println("Tempo médio de Espera: " + (sumTimeWait/filas.get(2).size()));
            this.output.println("Tempo médio de Turnaround: " + (sumTimeTurnaround/filas.get(2).size()));
            this.output.println("Tempo total de ultilização da CPU: " + executionTimeTotal);
            this.output.print("Taxa percentual da ocupação da CPU: ");
            BigDecimal aux = new BigDecimal(executionTimeTotal*100).divide(new BigDecimal(timeSystem),3,RoundingMode.UP);
            this.output.print(aux); 
            this.output.println("%");
            this.output.println("Tempo que a CPU permaneceu ociosa: " + (timeSystem - executionTimeTotal));
            this.output.print("Taxa percentual da ociosidade da CPU: ");
            aux = new BigDecimal((timeSystem - executionTimeTotal)*100).divide(new BigDecimal(timeSystem),3,RoundingMode.UP);
            this.output.print(aux);
            this.output.println("%");
        }
    }  
}
