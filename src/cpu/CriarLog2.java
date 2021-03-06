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
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author wellitongb
 */
public class CriarLog2 {
	private /*@ spec_public nullable @*/ final File diretorio = new File("."); 
    private /*@ spec_public nullable @*/ FileWriter arquivo;
    private /*@ spec_public nullable @*/ PrintWriter output;
    
    /**
     *Metodo construtor da classe CriarLog1.
     * @param typeLog Representa o nome do algoritmo usado para criar o log.
     */
    /*@ requires typeLog != null;
    @ 	assignable this.arquivo;
    @	assignable this.output;
    @	ensures this.arquivo != null;
    @	ensures this.output != null;
    @*/
    public CriarLog2(String typeLog){
        openFile(typeLog);
        this.output.println("/*********************************");
        this.output.println("* Componentes do Grupo: ");
        this.output.println("* ELISIO BRENO GARCIA CARDOSO");
        this.output.println("* JOSE WELLITON NUNES JUNIOR");
        this.output.println("* MOISES CAVALCANTE FERNANDES");
        this.output.println("* VICTOR SANTIAGO VALENTE");
        this.output.println("**********************************/");
    }
    
    /*@ private normal_behavior
    @	requires typeLog != null;
    @ 	assignable this.arquivo;
    @	assignable this.output;
    @	ensures this.arquivo != null;
    @	ensures this.output != null;
    @*/
    private void openFile(String typeLog){
        try{
            this.arquivo = new FileWriter(this.diretorio.getAbsolutePath().substring(0, this.diretorio.getAbsolutePath().length() - 1).concat(typeLog + " - LOG2.log"));
            this.output = new PrintWriter(this.arquivo);
        }
        catch (IOException ex) {
            System.out.println("Erro ao criar arquivo");
            Logger.getLogger(CriarLog1.class.getName()).log(Level.SEVERE, null, ex);
        }   
    }
    
    /*@	requires this.output != null;
    @ assignable \nothing;
    @*/
    public /*@ pure @*/ void close(){
        this.output.close();
    }
    
    /**
     * Metodo que imprimi as informacoes do processo exigidas para o primeiro LOG.
     * @param filas Representa as filas de PRONTO,ESPERA,FINALIZADO.
     * @param timeSystem Representa o tempo do sistema.
     * @throws NullPointerException Caso filas seja nulo.
     * @throws Error Caso o tamanho de filas seja diferente de 3.
     */
    /*@ requires filas != null;
    @	requires timeSystem > 0;
    @	assignable \nothing; 
    @*/
    public /*@ pure @*/ void print(ArrayList<ArrayList<Processo>> filas, int timeSystem){
        if(filas == null){
            throw new NullPointerException("Nao foi passado as filas exigidas para impressao");
        }
        if(filas.size() != 3){
            throw new Error("Nao foi passado o numero de filas exigidas para impressao");
        }
        if(timeSystem%200 == 0){
            this.output.print(filas.get(0).size() + " ");
            this.output.print(filas.get(1).size() + " ");
            this.output.println(filas.get(2).size() + " ");
        }
    }
}
